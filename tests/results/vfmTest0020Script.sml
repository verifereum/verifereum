Theory vfmTest0020[no_sig_docs]
Ancestors vfmTestDefs0020
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0020_0.nsv", "result0020_1.nsv", "result0020_2.nsv", "result0020_3.nsv"];
val thyn = "vfmTestDefs0020";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
