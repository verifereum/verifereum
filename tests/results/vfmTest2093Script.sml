Theory vfmTest2093[no_sig_docs]
Ancestors vfmTestDefs2093
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2093_0.nsv", "result2093_1.nsv", "result2093_2.nsv", "result2093_3.nsv", "result2093_4.nsv", "result2093_5.nsv", "result2093_6.nsv", "result2093_7.nsv", "result2093_8.nsv", "result2093_9.nsv", "result2093_10.nsv", "result2093_11.nsv"];
val thyn = "vfmTestDefs2093";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
