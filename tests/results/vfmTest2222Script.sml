Theory vfmTest2222[no_sig_docs]
Ancestors vfmTestDefs2222
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2222_0.nsv", "result2222_1.nsv", "result2222_2.nsv", "result2222_3.nsv", "result2222_4.nsv", "result2222_5.nsv", "result2222_6.nsv", "result2222_7.nsv", "result2222_8.nsv", "result2222_9.nsv", "result2222_10.nsv"];
val thyn = "vfmTestDefs2222";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
