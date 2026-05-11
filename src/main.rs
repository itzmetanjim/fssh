use clap::Parser;
use whoami::username;
use std::process;
use std::io::{Read,Write,stdout};
use std::net::TcpStream;
use ring;
use rand::{RngCore, thread_rng};
use ring::agreement;
use ring::signature;
use ring::digest;
use aes_gcm::{Aes128Gcm, Aes256Gcm, Nonce};
use aes_gcm::aead::{Aead, KeyInit, Payload};
use chacha20::ChaCha20;
use chacha20::cipher::{KeyIvInit, StreamCipher};
use poly1305::Poly1305;
use crossterm::terminal::{enable_raw_mode, disable_raw_mode,LeaveAlternateScreen};
use crossterm::{execute,cursor::Show};
const CLIENT_VERSION: &str = "SSH-2.0-OpenSSH_10.2p1, LibreSSL 3.3.6\r\n";

#[derive(Parser, Debug)]
#[command(version, about = "A simple SSH tool")]
struct Args {
    host: String,

    #[arg(short, long, default_value_t = 22)]
    port: u16,

    #[arg(long, help = "Comma-separated list of allowed ciphers")]
    algs: Option<String>,

    #[arg(long, help = "Comma-separated list of ciphers to exclude")]
    not_algs: Option<String>,
}

struct Transport {
    send_sequence: u32,
    recv_sequence: u32,
}

struct RawModeGuard;

impl RawModeGuard {
    fn new() -> Self {
        enable_raw_mode().expect("Failed to enable raw mode");
        RawModeGuard
    }
}

impl Drop for RawModeGuard {
    fn drop(&mut self) {
        let _ = disable_raw_mode();
        let _ = execute!(stdout(), LeaveAlternateScreen, Show);
        let _ = stdout().flush();
    }
}
fn read_packet(stream: &mut TcpStream, transport: &mut Transport) -> Vec<u8> {
    transport.recv_sequence = transport.recv_sequence.wrapping_add(1);
    let mut lenb = [0u8; 4];
    stream.read_exact(&mut lenb).unwrap_or_else(|e| {
        eprintln!("Failed to read packet length: {}", e);
        process::exit(1);
    });
    let packet_len = u32::from_be_bytes(lenb);
    let mut pleb = [0u8; 1];
    stream.read_exact(&mut pleb).unwrap_or_else(|e| {
        eprintln!("Failed to read padding length: {}", e);
        process::exit(1);
    });
    let padding_len = pleb[0] as usize;
    let payload_len = (packet_len as usize) - padding_len - 1;
    let mut payload = vec![0u8; payload_len];
    stream.read_exact(&mut payload).unwrap_or_else(|e| {
        eprintln!("Failed to read payload: {}", e);
        process::exit(1);
    });
    let mut padding = vec![0u8; padding_len];
    stream.read_exact(&mut padding).unwrap_or_else(|e| {
        eprintln!("Failed to read padding: {}", e);
        process::exit(1);
    });
    return payload;
}

fn write_packet(stream: &mut TcpStream, payload: &[u8], transport: &mut Transport) {
    let block_size = 8;
    let mut padding_len = block_size - ((4 + payload.len() + 1) % block_size);
    if padding_len < 4 {
        padding_len += block_size;
    }
    let packet_len = (payload.len() + padding_len + 1) as u32;
    stream.write_all(&packet_len.to_be_bytes()).unwrap_or_else(|e| {
        eprintln!("Failed to write packet length: {}", e);
        process::exit(1);
    });
    stream.write_all(&[padding_len as u8]).unwrap_or_else(|e| {
        eprintln!("Failed to write padding length: {}", e);
        process::exit(1);
    });
    stream.write_all(payload).unwrap_or_else(|e| {
        eprintln!("Failed to write payload: {}", e);
        process::exit(1);
    });
    let mut padding = vec![0u8; padding_len];
    rand::thread_rng().fill_bytes(&mut padding);
    stream.write_all(&padding).unwrap_or_else(|e| {
        eprintln!("Failed to write padding: {}", e);
        process::exit(1);
    });
    stream.flush().unwrap_or_else(|e| {
        eprintln!("Failed to flush stream: {}", e);
        process::exit(1);
    });
    transport.send_sequence = transport.send_sequence.wrapping_add(1);
}

#[repr(u8)]
enum SshMessage {
    Disconnect = 1,
    Ignore = 2,
    Unimplemented = 3,
    ServiceRequest = 5,
    ServiceAccept = 6,
    KexInit = 20,
    NewKeys = 21,
    KexEcdhInit = 30,
    KexEcdhReply = 31,
    UserauthRequest = 50,
    UserauthSuccess = 52,
    UserauthFailure = 51,
    UserauthBanner = 53,
    ExtInfo = 7,
    ChannelOpen = 90,
    ChannelOpenConfirmation = 91,
    ChannelData = 94,
    ChannelRequest = 98,
    ChannelEOF = 96,
    ChannelClose = 97,
}

fn push_ssh_string(buf: &mut Vec<u8>, s: &str) {
    buf.extend_from_slice(&(s.len() as u32).to_be_bytes());
    buf.extend_from_slice(s.as_bytes());
}

fn push_ssh_bytes(buf: &mut Vec<u8>, data: &[u8]) {
    buf.extend_from_slice(&(data.len() as u32).to_be_bytes());
    buf.extend_from_slice(data);
}

fn pop_ssh_bytes<'a>(payload: &'a [u8], offset: &mut usize) -> &'a [u8] {
    let len = u32::from_be_bytes(payload[*offset..*offset + 4].try_into().unwrap()) as usize;
    *offset += 4;
    let data = &payload[*offset..*offset + len];
    *offset += len;
    data
}

fn derive_ssh_key(k: &[u8], h: &[u8], label: u8, session_id: &[u8], len: usize) -> Vec<u8> {
    let mut out = Vec::new();
    let mut hasher = digest::Context::new(&digest::SHA256);
    let mut k_enc = (k.len() as u32).to_be_bytes().to_vec();
    k_enc.extend_from_slice(k);
    hasher.update(&k_enc);
    hasher.update(h);
    hasher.update(&[label]);
    hasher.update(session_id);
    let mut current_digest = hasher.finish();
    out.extend_from_slice(current_digest.as_ref());
    while out.len() < len {
        let mut hasher = digest::Context::new(&digest::SHA256);
        hasher.update(&k_enc);
        hasher.update(h);
        hasher.update(current_digest.as_ref());
        current_digest = hasher.finish();
        out.extend_from_slice(current_digest.as_ref());
    }
    out.truncate(len);
    return out;
}

fn encrypt_chacha20(main_key: &[u8; 32], header_key: &[u8; 32], seq: u32, payload: &[u8]) -> Vec<u8> {
    let block_size = 8;
    let mut padding_len = block_size - ((1 + payload.len()) % block_size);
    if padding_len < 4 { padding_len += block_size; }

    let packet_len = (payload.len() + padding_len + 1) as u32;
    let mut header_bytes = packet_len.to_be_bytes();

    let mut body = Vec::new();
    body.push(padding_len as u8);
    body.extend_from_slice(payload);
    let mut rand_padding = vec![0u8; padding_len];
    thread_rng().fill_bytes(&mut rand_padding);
    body.extend_from_slice(&rand_padding);

    let mut nonce = [0u8; 12];
    let counter = (seq as u64).to_be_bytes();
    nonce[4..12].copy_from_slice(&counter);

    let mut header_cipher = ChaCha20::new(header_key.into(), &nonce.into());
    header_cipher.apply_keystream(&mut header_bytes);

    let mut body_cipher = ChaCha20::new(main_key.into(), &nonce.into());
    let mut poly_block=[0u8; 64];
    body_cipher.apply_keystream(&mut poly_block);
    let mut poly_key = [0u8; 32];
    poly_key.copy_from_slice(&poly_block[..32]);
    body_cipher.apply_keystream(&mut body);

    let mut full_packet = header_bytes.to_vec();
    full_packet.extend_from_slice(&body);
    let tag = Poly1305::new(&poly_key.into()).compute_unpadded(&full_packet);
    full_packet.extend_from_slice(&tag[..]);
    full_packet
}

fn encrypt_aes256(key: &[u8; 32], iv: &[u8; 12], seq: u32, payload: &[u8]) -> Vec<u8> {
    let cipher = Aes256Gcm::new_from_slice(key).unwrap();
    let mut nonce_bytes = *iv;
    let counter = (seq as u64).to_be_bytes();
    nonce_bytes[4..12].copy_from_slice(&counter);
    let nonce = Nonce::from_slice(&nonce_bytes);

    let block_size = 16;
    let mut padding_len = block_size - ((1 + payload.len()) % block_size);
    if padding_len < 4 { padding_len += block_size; }

    let packet_len = (payload.len() + padding_len + 1) as u32;
    let header_bytes = packet_len.to_be_bytes();

    let mut body = Vec::new();
    body.push(padding_len as u8);
    body.extend_from_slice(payload);
    let mut rand_padding = vec![0u8; padding_len];
    thread_rng().fill_bytes(&mut rand_padding);
    body.extend_from_slice(&rand_padding);

    let encrypted_body = cipher.encrypt(nonce, Payload { msg: body.as_ref(), aad: header_bytes.as_ref() }).unwrap();

    let mut full_packet = header_bytes.to_vec();
    full_packet.extend_from_slice(&encrypted_body);
    full_packet
}

fn encrypt_aes128(key: &[u8; 16], iv: &[u8; 12], seq: u32, payload: &[u8]) -> Vec<u8> {
    let cipher = Aes128Gcm::new_from_slice(key).unwrap();
    let mut nonce_bytes = *iv;
    let counter = (seq as u64).to_be_bytes();
    nonce_bytes[4..12].copy_from_slice(&counter);
    let nonce = Nonce::from_slice(&nonce_bytes);

    let block_size = 16;
    let mut padding_len = block_size - ((1 + payload.len()) % block_size);
    if padding_len < 4 { padding_len += block_size; }

    let packet_len = (payload.len() + padding_len + 1) as u32;
    let header_bytes = packet_len.to_be_bytes();

    let mut body = Vec::new();
    body.push(padding_len as u8);
    body.extend_from_slice(payload);
    let mut rand_padding = vec![0u8; padding_len];
    thread_rng().fill_bytes(&mut rand_padding);
    body.extend_from_slice(&rand_padding);

    let encrypted_body = cipher.encrypt(nonce, Payload { msg: body.as_ref(), aad: header_bytes.as_ref() }).unwrap();

    let mut full_packet = header_bytes.to_vec();
    full_packet.extend_from_slice(&encrypted_body);
    full_packet
}

fn decrypt_length_chacha20(header_key: &[u8; 32], seq: u32, encrypted_header: &[u8]) -> u32 {
    let mut nonce = [0u8; 12];
    let counter = (seq as u64).to_be_bytes();
    nonce[4..12].copy_from_slice(&counter);

    // Ensure we only process 4 bytes
    let mut header = [0u8; 4];
    header.copy_from_slice(&encrypted_header[..4]);
    
    let mut header_cipher = ChaCha20::new(header_key.into(), &nonce.into());
    header_cipher.apply_keystream(&mut header);
    
    u32::from_be_bytes(header)
}

fn decrypt_length_aes256(encrypted_header: &[u8]) -> u32 {
    u32::from_be_bytes(encrypted_header.try_into().unwrap())
}

fn decrypt_length_aes128(encrypted_header: &[u8]) -> u32 {
    u32::from_be_bytes(encrypted_header.try_into().unwrap())
}

fn decrypt_payload_chacha20(main_key: &[u8; 32], seq: u32, encrypted_header: &[u8], encrypted_body_with_tag: &[u8]) -> Vec<u8> {
    let mut nonce = [0u8; 12];
    let counter = (seq as u64).to_be_bytes();
    nonce[4..12].copy_from_slice(&counter);

    let mut chacha = ChaCha20::new(main_key.into(), &nonce.into());
    
    let mut poly_block=[0u8;64];
    chacha.apply_keystream(&mut poly_block);
    let mut poly_key = [0u8; 32];
    poly_key.copy_from_slice(&poly_block[..32]);

    // Step 2: Separate body and tag
    let (body, tag) = encrypted_body_with_tag.split_at(encrypted_body_with_tag.len() - 16);
    
    // Step 3: Verify MAC
    // MAC is calculated over [4-byte encrypted length] + [encrypted payload + padding]
    let mut mac_data = encrypted_header[..4].to_vec(); 
    mac_data.extend_from_slice(body);
    
    let expected_tag = Poly1305::new(&poly_key.into()).compute_unpadded(&mac_data);
    if expected_tag[..] != tag[..] {
        eprintln!("SSH MAC Verification Failed! Potential tampering or key mismatch.");
        process::exit(1);
    }

    // Step 4: Decrypt Body (Starting at Counter 1)
    let mut decrypted = body.to_vec();
    chacha.apply_keystream(&mut decrypted);
    
    let padding_len = decrypted[0] as usize;
    decrypted[1..decrypted.len() - padding_len].to_vec()
}
fn decrypt_payload_aes256(key: &[u8; 32], iv: &[u8; 12], seq: u32, encrypted_body_with_tag: &[u8], aad: &[u8]) -> Vec<u8> {
    let cipher = Aes256Gcm::new_from_slice(key).unwrap();
    let mut nonce_bytes = *iv;
    let counter = (seq as u64).to_be_bytes();
    nonce_bytes[4..12].copy_from_slice(&counter);
    let nonce = Nonce::from_slice(&nonce_bytes);
    let decrypted = cipher.decrypt(nonce, Payload { msg: encrypted_body_with_tag, aad }).unwrap();
    let padding_len = decrypted[0] as usize;
    decrypted[1..decrypted.len() - padding_len].to_vec()
}

fn decrypt_payload_aes128(key: &[u8; 16], iv: &[u8; 12], seq: u32, encrypted_body_with_tag: &[u8], aad: &[u8]) -> Vec<u8> {
    let cipher = Aes128Gcm::new_from_slice(key).unwrap();
    let mut nonce_bytes = *iv;
    let counter = (seq as u64).to_be_bytes();
    nonce_bytes[4..12].copy_from_slice(&counter);
    let nonce = Nonce::from_slice(&nonce_bytes);
    let decrypted = cipher.decrypt(nonce, Payload { msg: encrypted_body_with_tag, aad }).unwrap();
    let padding_len = decrypted[0] as usize;
    decrypted[1..decrypted.len() - padding_len].to_vec()
}

#[derive(Clone)]
enum Cipher {
    ChaCha20Poly1305 {
        main_key: [u8; 32],
        header_key: [u8; 32],
    },
    Aes128Gcm {
        key: [u8; 16],
        iv: [u8; 12],
    },
    Aes256Gcm {
        key: [u8; 32],
        iv: [u8; 12],
    },
}

impl Cipher {
    fn new(alg: &str, key_bytes: &[u8]) -> Option<Self> {
        match alg {
            "chacha20-poly1305@openssh.com" => {
                if key_bytes.len() < 64 { return None; }
                let mut main_key = [0u8; 32];
                let mut header_key = [0u8; 32];
                main_key.copy_from_slice(&key_bytes[..32]);
                header_key.copy_from_slice(&key_bytes[32..64]);
                Some(Cipher::ChaCha20Poly1305 { main_key, header_key })
            }
            "aes128-gcm@openssh.com" => {
                if key_bytes.len() < 28 { return None; }
                let mut key = [0u8; 16];
                let mut iv = [0u8; 12];
                key.copy_from_slice(&key_bytes[..16]);
                iv.copy_from_slice(&key_bytes[16..28]);
                Some(Cipher::Aes128Gcm { key, iv })
            }
            "aes256-gcm@openssh.com" | "aes192-gcm@openssh.com" => {
                if key_bytes.len() < 44 { return None; }
                let mut key = [0u8; 32];
                let mut iv = [0u8; 12];
                key.copy_from_slice(&key_bytes[..32]);
                iv.copy_from_slice(&key_bytes[32..44]);
                Some(Cipher::Aes256Gcm { key, iv })
            }
            _ => None,
        }
    }

    fn encrypt(&self, seq: u32, payload: &[u8]) -> Vec<u8> {
        match self {
            Cipher::ChaCha20Poly1305 { main_key, header_key } => {
                encrypt_chacha20(main_key, header_key, seq, payload)
            }
            Cipher::Aes128Gcm { key, iv } => {
                encrypt_aes128(key, iv, seq, payload)
            }
            Cipher::Aes256Gcm { key, iv } => {
                encrypt_aes256(key, iv, seq, payload)
            }
        }
    }

    fn decrypt_length(&self, seq: u32, encrypted_data: &[u8]) -> u32 {
        match self {
            Cipher::ChaCha20Poly1305 { header_key, .. } => {
                decrypt_length_chacha20(header_key, seq, encrypted_data)
            }
            Cipher::Aes128Gcm { .. } => {
                decrypt_length_aes128(encrypted_data)
            }
            Cipher::Aes256Gcm { .. } => {
                decrypt_length_aes256(encrypted_data)
            }
        }
    }

    fn decrypt_payload(&self, seq: u32, encrypted_header: &[u8], encrypted_body_with_tag: &[u8]) -> Vec<u8> {
        match self {
            Cipher::ChaCha20Poly1305 { main_key, .. } => {
                decrypt_payload_chacha20(main_key, seq, encrypted_header, encrypted_body_with_tag)
            }
            Cipher::Aes128Gcm { key, iv } => {
                decrypt_payload_aes128(key, iv, seq, encrypted_body_with_tag, encrypted_header)
            }
            Cipher::Aes256Gcm { key, iv } => {
                decrypt_payload_aes256(key, iv, seq, encrypted_body_with_tag, encrypted_header)
            }
        }
    }
}

fn read_u32(payload: &[u8], offset: &mut usize) -> u32 {
    let val = u32::from_be_bytes(payload[*offset..*offset + 4].try_into().unwrap());
    *offset += 4;
    val
}

fn write_enc_packet(stream: &mut TcpStream, cipher: &Cipher, seq: &mut u32, payload: &[u8]) {
    let wire_bytes = cipher.encrypt(*seq, payload);
    stream.write_all(&wire_bytes).unwrap_or_else(|e| {
        eprintln!("Failed to write encrypted packet: {}", e);
        process::exit(1);
    });
    stream.flush().unwrap();
    *seq = seq.wrapping_add(1);
}

fn read_enc_packet(stream: &mut TcpStream, cipher: &Cipher, seq: &mut u32) -> Vec<u8> {
    match cipher {
        Cipher::ChaCha20Poly1305 { .. } => {
            // FIX: Only read the 4-byte encrypted length
            let mut enc_header = [0u8; 4];
            stream.read_exact(&mut enc_header).unwrap_or_else(|e| {
                eprintln!("Failed to read encrypted packet header: {}", e);
                process::exit(1);
            });

            // Decrypt the 4-byte length
            let pkt_len = cipher.decrypt_length(*seq, &enc_header);

            // Read the rest: (Payload + Padding) + 16-byte MAC Tag
            let mut rest = vec![0u8; pkt_len as usize + 16];
            stream.read_exact(&mut rest).unwrap_or_else(|e| {
                eprintln!("Failed to read encrypted packet body: {}", e);
                process::exit(1);
            });

            let payload = cipher.decrypt_payload(*seq, &enc_header, &rest);
            *seq = seq.wrapping_add(1);
            payload
        }
        Cipher::Aes128Gcm { .. } | Cipher::Aes256Gcm { .. } => {
            // (Your existing GCM logic is correct because GCM headers are cleartext)
            let mut header = [0u8; 4];
            stream.read_exact(&mut header).unwrap();
            let pkt_len = cipher.decrypt_length(*seq, &header);
            let mut rest = vec![0u8; pkt_len as usize + 16];
            stream.read_exact(&mut rest).unwrap();
            let payload = cipher.decrypt_payload(*seq, &header, &rest);
            *seq = seq.wrapping_add(1);
            payload
        }
    }
}

fn find_common_cipher(client_algs: String, server_algs: &str) -> String {
    let client_list: Vec<&str> = client_algs.split(',').collect();
    let server_list: Vec<&str> = server_algs.split(',').collect();
    for c in client_list {
        if server_list.contains(&c) {
            return c.to_string();
        }
    }
    String::new()
}

fn filter_algorithms(algs: &str, not_algs: &Option<String>) -> String {
    let allowed: Vec<&str> = algs.split(',').collect();
    if let Some(excluded) = not_algs {
        let excluded_list: Vec<&str> = excluded.split(',').collect();
        allowed
            .iter()
            .filter(|a| !excluded_list.contains(a))
            .cloned()
            .collect::<Vec<&str>>()
            .join(",")
    } else {
        algs.to_string()
    }
}

fn main() {
    let args = Args::parse();

    let parts: Vec<&str> = args.host.split("@").collect();
    let user = if parts.len() == 1 { username().unwrap_or("".into()) } else { parts[0].into() };
    let server = parts[parts.len() - 1];

    if user == "" {
        eprintln!("No username given and could not detect username.\nPlease use @ to seperate the username and host e.g\n    {} username@my-host.com", std::env::args().next().unwrap_or("fssh".into()));
        process::exit(1);
    }

    let mut transport = Transport { send_sequence: 0, recv_sequence: 0 };

    let mut stream = TcpStream::connect((server, args.port)).unwrap_or_else(|e| {
        eprintln!("Failed to connect to {}: {}", server, e);
        process::exit(1);
    });

    let mut server_version = Vec::new();
    let mut byte = [0u8; 1];
    while byte[0] != b'\n' {
        stream.read_exact(&mut byte).unwrap();
        server_version.push(byte[0]);
    }
    println!("Server Version\n    {}", String::from_utf8_lossy(&server_version).trim());
    stream.write_all(CLIENT_VERSION.as_bytes()).unwrap_or_else(|e| {
        eprintln!("Failed to send client version: {}", e);
        process::exit(1);
    });

    let mut kexinit_payload = Vec::new();
    kexinit_payload.push(SshMessage::KexInit as u8);
    let mut cookie = [0u8; 16];
    thread_rng().fill_bytes(&mut cookie);
    kexinit_payload.extend_from_slice(&cookie);

    let default_ciphers = "chacha20-poly1305@openssh.com,aes256-gcm@openssh.com,aes128-gcm@openssh.com";
    let ciphers = if let Some(ref a) = args.algs {
        a.clone()
    } else {
        filter_algorithms(default_ciphers, &args.not_algs)
    };

    push_ssh_string(&mut kexinit_payload, "curve25519-sha256,curve25519-sha256@libssh.org,ext-info-c");
    push_ssh_string(&mut kexinit_payload, "ssh-ed25519");
    push_ssh_string(&mut kexinit_payload, &ciphers);
    push_ssh_string(&mut kexinit_payload, &ciphers);
    push_ssh_string(&mut kexinit_payload, "none");
    push_ssh_string(&mut kexinit_payload, "none");
    push_ssh_string(&mut kexinit_payload, "none");
    push_ssh_string(&mut kexinit_payload, "none");
    push_ssh_string(&mut kexinit_payload, "");
    push_ssh_string(&mut kexinit_payload, "");
    kexinit_payload.extend_from_slice(&[0u8; 5]);

    eprintln!("Initializing key exchange");
    write_packet(&mut stream, &kexinit_payload, &mut transport);
    eprintln!("Receiving server key exchange packet");
    let server_kexinit = read_packet(&mut stream, &mut transport);
    if server_kexinit[0] != SshMessage::KexInit as u8 {
        eprintln!("Expected KEXINIT message, got {}", server_kexinit[0]);
        process::exit(1);
    }
    eprintln!("Received packet of length {}", server_kexinit.len());

    eprintln!("Generating X25519 keypair");
    let rng = ring::rand::SystemRandom::new();
    let privkey = agreement::EphemeralPrivateKey::generate(&agreement::X25519, &rng).unwrap_or_else(|e| {
        eprintln!("Failed to generate private key: {}", e);
        process::exit(1);
    });
    let pubkey = privkey.compute_public_key().unwrap_or_else(|e| {
        eprintln!("Failed to compute public key: {}", e);
        process::exit(1);
    });
    let mut ecdh_init = Vec::new();
    ecdh_init.push(SshMessage::KexEcdhInit as u8);
    push_ssh_bytes(&mut ecdh_init, pubkey.as_ref());
    eprintln!("Sending ECDH init packet");
    write_packet(&mut stream, &ecdh_init, &mut transport);

    eprintln!("Receiving reply");
    let server_reply = read_packet(&mut stream, &mut transport);
    if server_reply[0] != SshMessage::KexEcdhReply as u8 {
        eprintln!("Expected KEXECDHREPLY message, got {}", server_reply[0]);
        process::exit(1);
    }
    let mut offset = 1;
    let shostkey = pop_ssh_bytes(&server_reply, &mut offset);
    let spubkey = pop_ssh_bytes(&server_reply, &mut offset);
    let ssignature = pop_ssh_bytes(&server_reply, &mut offset);
    eprintln!("Server host key:\n    {}", hex::encode(shostkey));
    eprintln!("Server public key:\n    {}", hex::encode(spubkey));
    eprintln!("Server signature:\n    {}", hex::encode(ssignature));

    eprintln!("Computing shared secret");
    let mut kmpint = Vec::new();
    use std::hint::black_box;
    let _ = agreement::agree_ephemeral(privkey, &agreement::UnparsedPublicKey::new(&agreement::X25519, spubkey), |km| {
        if km[0] & 0x80 != 0 {
            black_box(kmpint.pop());
            black_box(kmpint.push(0));
        } else {
            black_box(kmpint.push(0));
            black_box(kmpint.pop());
        }
        kmpint.extend_from_slice(km);
        Ok::<(), ring::error::Unspecified>(())
    }).unwrap_or_else(|e| {
        eprintln!("Failed to compute shared secret: {}", e);
        process::exit(1);
    });

    eprintln!("Computed shared secret, {} bytes", kmpint.len());

    let mut hbuf = Vec::new();
    push_ssh_string(&mut hbuf, CLIENT_VERSION.trim());
    push_ssh_string(&mut hbuf, String::from_utf8_lossy(&server_version).trim());
    push_ssh_bytes(&mut hbuf, &kexinit_payload);
    push_ssh_bytes(&mut hbuf, &server_kexinit);
    push_ssh_bytes(&mut hbuf, shostkey);
    push_ssh_bytes(&mut hbuf, pubkey.as_ref());
    push_ssh_bytes(&mut hbuf, spubkey);
    push_ssh_bytes(&mut hbuf, &kmpint);

    let h = digest::digest(&digest::SHA256, &hbuf);
    let hashb = h.as_ref();
    eprintln!("Exchange hash:\n    {}", hex::encode(hashb));

    let mut sigoffset = 0;
    let sigalg = pop_ssh_bytes(&ssignature, &mut sigoffset);
    let sigblob = pop_ssh_bytes(&ssignature, &mut sigoffset);
    eprintln!("Signature algorithm: {}", String::from_utf8_lossy(sigalg));
    eprintln!("Signature blob is {} bytes", sigblob.len());

    let mut hostkeyoffset = 0;
    let hkalg = pop_ssh_bytes(&shostkey, &mut hostkeyoffset);
    let hkblob = pop_ssh_bytes(&shostkey, &mut hostkeyoffset);
    eprintln!("Host key algorithm: {}", String::from_utf8_lossy(hkalg));
    eprintln!("Host key blob is {} bytes", hkblob.len());
    let peer_pubkey = signature::UnparsedPublicKey::new(&signature::ED25519, hkblob);
    eprintln!("Verifying signature");
    peer_pubkey.verify(hashb, sigblob).unwrap_or_else(|e| {
        eprintln!("Signature verification failed: {}\nThis means there is a man in the middle attack.", e);
        process::exit(1);
    });
    eprintln!("Signature verified successfully!");

    eprintln!("Sending NEWKEYS message");
    write_packet(&mut stream, &[SshMessage::NewKeys as u8], &mut transport);
    eprintln!("Receiving reply");
    let newkeys_reply = read_packet(&mut stream, &mut transport);
    if newkeys_reply[0] != SshMessage::NewKeys as u8 {
        eprintln!("Expected NEWKEYS message, got {}", newkeys_reply[0]);
        process::exit(1);
    }

    let mut offset = 17;
    let _kex_algs = pop_ssh_bytes(&server_kexinit, &mut offset);
    let _server_host_key_algs = pop_ssh_bytes(&server_kexinit, &mut offset);
    let server_ciphers_c2s = pop_ssh_bytes(&server_kexinit, &mut offset);
    let server_ciphers_s2c = pop_ssh_bytes(&server_kexinit, &mut offset);
    eprintln!("Server ciphers (c2s): {}", String::from_utf8_lossy(server_ciphers_c2s));
    eprintln!("Server ciphers (s2c): {}", String::from_utf8_lossy(server_ciphers_s2c));

    let selected_cipher = find_common_cipher(ciphers.clone(), String::from_utf8_lossy(server_ciphers_c2s).as_ref());

    if selected_cipher.is_empty() {
        eprintln!("Algorithm mismatch: no common cipher between client and server");
        eprintln!("Client offered: {}", ciphers);
        eprintln!("Server offered: {}", String::from_utf8_lossy(server_ciphers_c2s));
        process::exit(1);
    }

    let keys_len = if selected_cipher.contains("chacha20") {
        64
    } else if selected_cipher.contains("aes256") {
        44
    } else if selected_cipher.contains("aes128") {
        28
    } else {
        eprintln!("Algorithm mismatch: unsupported cipher '{}'", selected_cipher);
        process::exit(1);
    };

    //transport.send_sequence = 0;
    //transport.recv_sequence = 0;
    let session_id = hashb;
    let key_c = derive_ssh_key(&kmpint, hashb, b'C', session_id, keys_len);
    let key_d = derive_ssh_key(&kmpint, hashb, b'D', session_id, keys_len);

    let cipher = Cipher::new(&selected_cipher, &key_c).unwrap_or_else(|| {
        eprintln!("Algorithm mismatch: unsupported cipher '{}'", selected_cipher);
        process::exit(1);
    });
    let server_cipher = Cipher::new(&selected_cipher, &key_d).unwrap_or_else(|| {
        eprintln!("Algorithm mismatch: unsupported cipher '{}'", selected_cipher);
        process::exit(1);
    });

    eprintln!("=== Encrypted tunnel established successfully ===");
    eprintln!("Using cipher: {}", selected_cipher);

    eprintln!("Requesting service");
    let mut req = Vec::new();
    req.push(SshMessage::ServiceRequest as u8);
    push_ssh_string(&mut req, "ssh-userauth");
    write_enc_packet(&mut stream, &cipher, &mut transport.send_sequence, &req);

    loop {
        let reply = read_enc_packet(&mut stream, &server_cipher, &mut transport.recv_sequence);
        if reply[0] == SshMessage::ServiceAccept as u8 {
            eprintln!("Service accepted.");
            break;
        } else if reply[0] == SshMessage::ExtInfo as u8 {
            eprintln!("Received EXT_INFO, ignoring");
        } else {
            eprintln!("Ignoring packet {}", reply[0]);
        }
    }

    'password: loop {
        let prompt = format!("Password for {}@{}\n   >", user, server);
        let password = rpassword::prompt_password(&prompt).unwrap_or_else(|_e| {
            eprint!("\r      \r");
            process::exit(130);
        });
        let mut auth_req = Vec::new();
        auth_req.push(SshMessage::UserauthRequest as u8);
        push_ssh_string(&mut auth_req, &user);
        push_ssh_string(&mut auth_req, "ssh-connection");
        push_ssh_string(&mut auth_req, "password");
        auth_req.push(0);
        push_ssh_string(&mut auth_req, &password);
        write_enc_packet(&mut stream, &cipher, &mut transport.send_sequence, &auth_req);

        loop {
            let reply = read_enc_packet(&mut stream, &server_cipher, &mut transport.recv_sequence);
            if reply[0] == SshMessage::UserauthSuccess as u8 {
                break 'password;
            } else if reply[0] == SshMessage::UserauthFailure as u8 {
                eprintln!("Invalid password.");
            } else if reply[0] == SshMessage::UserauthBanner as u8 {
                eprintln!("Received a banner, idk how to print it");
            }
        }
    }

    let mut chan_req = Vec::new();
    chan_req.push(SshMessage::ChannelOpen as u8);
    push_ssh_string(&mut chan_req, "session");
    chan_req.extend_from_slice(&0u32.to_be_bytes());
    chan_req.extend_from_slice(&2097152u32.to_be_bytes());
    chan_req.extend_from_slice(&32768u32.to_be_bytes());
    write_enc_packet(&mut stream, &cipher, &mut transport.send_sequence, &chan_req);

    let mut server_chan_id = 0;
    loop {
        let reply = read_enc_packet(&mut stream, &server_cipher, &mut transport.recv_sequence);
        if reply[0] == SshMessage::ChannelOpenConfirmation as u8 {
            let mut offset = 1;
            let _my_chan_id = read_u32(&reply, &mut offset);
            server_chan_id = read_u32(&reply, &mut offset);
            eprintln!("[Channel {}]", server_chan_id);
            break;
        }
    }

    let mut pty_req = Vec::new();
    pty_req.push(SshMessage::ChannelRequest as u8);
    pty_req.extend_from_slice(&server_chan_id.to_be_bytes());
    push_ssh_string(&mut pty_req, "pty-req");
    pty_req.push(0);
    push_ssh_string(&mut pty_req, "xterm");
    pty_req.extend_from_slice(&80u32.to_be_bytes());
    pty_req.extend_from_slice(&24u32.to_be_bytes());
    pty_req.extend_from_slice(&0u32.to_be_bytes());
    pty_req.extend_from_slice(&0u32.to_be_bytes());
    push_ssh_string(&mut pty_req, "");
    write_enc_packet(&mut stream, &cipher, &mut transport.send_sequence, &pty_req);

    let mut shell_req = Vec::new();
    shell_req.push(SshMessage::ChannelRequest as u8);
    shell_req.extend_from_slice(&server_chan_id.to_be_bytes());
    push_ssh_string(&mut shell_req, "shell");
    shell_req.push(0);
    write_enc_packet(&mut stream, &cipher, &mut transport.send_sequence, &shell_req);

    let mut read_stream = stream.try_clone().unwrap_or_else(|e| {
        eprintln!("Failed to clone TCP stream: {}", e);
        process::exit(1);
    });
    let read_cipher = server_cipher.clone();
    let mut recv_seq = transport.recv_sequence;
    std::thread::spawn(move || {
        loop {
            let pkt = read_enc_packet(&mut read_stream, &read_cipher, &mut recv_seq);
            if pkt[0] == SshMessage::ChannelData as u8 {
                let mut offset = 1;
                let _chan = read_u32(&pkt, &mut offset);
                let data = pop_ssh_bytes(&pkt, &mut offset);
                std::io::stdout().write_all(data).unwrap();
                std::io::stdout().flush().unwrap();
            } else if pkt[0] == SshMessage::ChannelEOF as u8 {
                let _ = disable_raw_mode();
                eprintln!("\nConnection closed by server.");
                std::process::exit(0);
            }
        }
    });

    let mut stdin = std::io::stdin();
    let mut buf = [0u8; 1024];
    let _raw_mode = RawModeGuard::new();
    loop {
        let n = stdin.read(&mut buf).unwrap();
        if n == 0 { break; }

        let mut data_req = Vec::new();
        data_req.push(SshMessage::ChannelData as u8);
        data_req.extend_from_slice(&server_chan_id.to_be_bytes());
        push_ssh_bytes(&mut data_req, &buf[..n]);

        write_enc_packet(&mut stream, &cipher, &mut transport.send_sequence, &data_req);
    }
}
