// X8 helper (written for this measurement; not third-party): the cva6 cv32a6_imac_sv32 configuration with the
// data cache switched from HPDCACHE_WT (a git submodule absent from the pinned tree) to the in-tree WT cache, so
// that the whole core elaborates from the fetched files. Used as `CVA6Cfg=x8_cva6_cfg_pkg::Cfg`.
package x8_cva6_cfg_pkg;
  function automatic config_pkg::cva6_user_cfg_t mk();
    config_pkg::cva6_user_cfg_t c;
    c = cva6_config_pkg::cva6_cfg;
    c.DCacheType = config_pkg::WT;
    return c;
  endfunction
  localparam config_pkg::cva6_cfg_t Cfg = build_config_pkg::build_config(mk());
endpackage
