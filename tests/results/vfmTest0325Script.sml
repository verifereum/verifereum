Theory vfmTest0325[no_sig_docs]
Ancestors vfmTestDefs0325
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0325_0.nsv", "result0325_1.nsv"];
val thyn = "vfmTestDefs0325";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
