Theory vfmTest2261[no_sig_docs]
Ancestors vfmTestDefs2261
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2261_0.nsv", "result2261_1.nsv", "result2261_2.nsv", "result2261_3.nsv", "result2261_4.nsv", "result2261_5.nsv", "result2261_6.nsv", "result2261_7.nsv", "result2261_8.nsv"];
val thyn = "vfmTestDefs2261";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
