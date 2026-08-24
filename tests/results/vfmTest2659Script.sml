Theory vfmTest2659[no_sig_docs]
Ancestors vfmTestDefs2659
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2659_0.nsv", "result2659_1.nsv", "result2659_2.nsv", "result2659_3.nsv"];
val thyn = "vfmTestDefs2659";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
