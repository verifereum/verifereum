Theory vfmTest0047[no_sig_docs]
Ancestors vfmTestDefs0047
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0047_0.nsv"];
val thyn = "vfmTestDefs0047";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
