# The model checks of the port mapping crate added with the trace tests of the PR line, sourced by scripts/proofs.sh after
# tlc.sh (which holds the models before them): one line per TLC config under proofs/tla.
par run_tlc portmap_addr PortMapAddr PortMapAddr
par witness_tlc portmap_addr_mapped PortMapAddr PortMapAddr_mapped NoMappedRefused
par run_tlc portmap_fallback PortMapFallback PortMapFallback
par witness_tlc portmap_fallback_full PortMapFallback PortMapFallback_full NoUpnpWithGateway
par run_tlc portmap_text PortMapText PortMapText
par witness_tlc portmap_text_full PortMapText PortMapText_full NoLaterFit
par run_tlc portmap_upnp PortMapUpnp PortMapUpnp
par witness_tlc portmap_upnp_foreign PortMapUpnp PortMapUpnp_foreign NoForeignRefused
