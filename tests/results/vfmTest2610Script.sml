Theory vfmTest2610[no_sig_docs]
Ancestors vfmTestDefs2610
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2610_0.nsv", "result2610_1.nsv", "result2610_2.nsv", "result2610_3.nsv"];
val thyn = "vfmTestDefs2610";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
