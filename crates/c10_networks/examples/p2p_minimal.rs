use libp2p::{
    Multiaddr, PeerId, Transport,
    core::upgrade,
    gossipsub, identify, identity, kad, noise, ping,
    swarm::{NetworkBehaviour, SwarmEvent},
    tcp, yamux,
};
use std::time::Duration;

#[derive(NetworkBehaviour)]
struct MyBehaviour {
    gossipsub: gossipsub::Behaviour,
    kademlia: kad::Behaviour<kad::store::MemoryStore>,
    ping: ping::Behaviour,
    identify: identify::Behaviour,
}

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    let key = identity::Keypair::generate_ed25519();
    let local_peer_id = PeerId::from(key.public());
    println!("local peer id: {}", local_peer_id);

    // 构建 TCP + Noise + Yamux 传输
    let tcp_transport = tcp::tokio::Transport::new(tcp::Config::default().nodelay(true));
    let noise = noise::Config::new(&key).expect("noise");
    let muxer = yamux::Config::default();
    let transport = tcp_transport
        .upgrade(upgrade::Version::V1)
        .authenticate(noise)
        .multiplex(muxer)
        .boxed();

    let gossipsub = gossipsub::Behaviour::new(
        gossipsub::MessageAuthenticity::Signed(key.clone()),
        gossipsub::Config::default(),
    )
    .map_err(anyhow::Error::msg)?;

    let store = kad::store::MemoryStore::new(local_peer_id);
    let kademlia = kad::Behaviour::new(local_peer_id, store);
    let ping = ping::Behaviour::default();
    let identify = identify::Behaviour::new(identify::Config::new("c10/1.0".into(), key.public()));

    let topic = gossipsub::IdentTopic::new("c10-demo");
    let mut behaviour = MyBehaviour {
        gossipsub,
        kademlia,
        ping,
        identify,
    };
    let _ = behaviour.gossipsub.subscribe(&topic);
    let mut swarm = libp2p::Swarm::new(
        transport,
        behaviour,
        local_peer_id,
        libp2p::swarm::Config::with_tokio_executor(),
    );

    libp2p::Swarm::listen_on(&mut swarm, "/ip4/0.0.0.0/tcp/0".parse::<Multiaddr>()?)?;

    let mut ticker = tokio::time::interval(Duration::from_secs(5));

    loop {
        tokio::select! {
            _ = ticker.tick() => {
                let _ = swarm.behaviour_mut().gossipsub.publish(topic.clone(), b"hello from c10".as_slice());
            }
            event = futures::StreamExt::select_next_some(&mut swarm) => {
                match event {
                    SwarmEvent::NewListenAddr { address, .. } => {
                        println!("listening on {}", address);
                    }
                    SwarmEvent::Behaviour(_ev) => {
                        // 可扩展处理其他事件
                    }
                    _ => {}
                }
            }
        }
    }
}
