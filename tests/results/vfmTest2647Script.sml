Theory vfmTest2647[no_sig_docs]
Ancestors vfmTestDefs2647
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2647_0.nsv", "result2647_1.nsv", "result2647_2.nsv", "result2647_3.nsv"];
val thyn = "vfmTestDefs2647";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
