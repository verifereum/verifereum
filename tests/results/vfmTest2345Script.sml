Theory vfmTest2345[no_sig_docs]
Ancestors vfmTestDefs2345
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2345_0.nsv", "result2345_1.nsv", "result2345_2.nsv", "result2345_3.nsv", "result2345_4.nsv", "result2345_5.nsv"];
val thyn = "vfmTestDefs2345";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
