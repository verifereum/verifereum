Theory vfmTest0781[no_sig_docs]
Ancestors vfmTestDefs0781
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0781_0.nsv", "result0781_1.nsv"];
val thyn = "vfmTestDefs0781";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
