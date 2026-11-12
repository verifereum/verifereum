Theory vfmTest2167[no_sig_docs]
Ancestors vfmTestDefs2167
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2167_0.nsv", "result2167_1.nsv", "result2167_2.nsv", "result2167_3.nsv", "result2167_4.nsv", "result2167_5.nsv", "result2167_6.nsv", "result2167_7.nsv", "result2167_8.nsv", "result2167_9.nsv", "result2167_10.nsv", "result2167_11.nsv", "result2167_12.nsv", "result2167_13.nsv"];
val thyn = "vfmTestDefs2167";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
