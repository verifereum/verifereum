Theory vfmTest2301[no_sig_docs]
Ancestors vfmTestDefs2301
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2301_0.nsv", "result2301_1.nsv", "result2301_2.nsv", "result2301_3.nsv", "result2301_4.nsv", "result2301_5.nsv", "result2301_6.nsv", "result2301_7.nsv"];
val thyn = "vfmTestDefs2301";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
