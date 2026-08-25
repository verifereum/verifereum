Theory vfmTest0700[no_sig_docs]
Ancestors vfmTestDefs0700
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0700_0.nsv"];
val thyn = "vfmTestDefs0700";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
