Theory vfmTest2311[no_sig_docs]
Ancestors vfmTestDefs2311
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2311_0.nsv", "result2311_1.nsv", "result2311_2.nsv", "result2311_3.nsv", "result2311_4.nsv", "result2311_5.nsv", "result2311_6.nsv", "result2311_7.nsv", "result2311_8.nsv", "result2311_9.nsv", "result2311_10.nsv", "result2311_11.nsv", "result2311_12.nsv", "result2311_13.nsv"];
val thyn = "vfmTestDefs2311";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
