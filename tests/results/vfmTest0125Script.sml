Theory vfmTest0125[no_sig_docs]
Ancestors vfmTestDefs0125
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0125_0.nsv", "result0125_1.nsv"];
val thyn = "vfmTestDefs0125";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
