Theory vfmTest2411[no_sig_docs]
Ancestors vfmTestDefs2411
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2411_0.nsv", "result2411_1.nsv", "result2411_2.nsv", "result2411_3.nsv", "result2411_4.nsv", "result2411_5.nsv", "result2411_6.nsv", "result2411_7.nsv"];
val thyn = "vfmTestDefs2411";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
