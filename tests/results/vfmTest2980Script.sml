Theory vfmTest2980[no_sig_docs]
Ancestors vfmTestDefs2980
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2980_0.nsv", "result2980_1.nsv", "result2980_2.nsv", "result2980_3.nsv", "result2980_4.nsv", "result2980_5.nsv"];
val thyn = "vfmTestDefs2980";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
