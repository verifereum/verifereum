Theory vfmTest2418[no_sig_docs]
Ancestors vfmTestDefs2418
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2418_0.nsv", "result2418_1.nsv", "result2418_2.nsv", "result2418_3.nsv", "result2418_4.nsv", "result2418_5.nsv", "result2418_6.nsv", "result2418_7.nsv", "result2418_8.nsv", "result2418_9.nsv", "result2418_10.nsv", "result2418_11.nsv", "result2418_12.nsv", "result2418_13.nsv", "result2418_14.nsv", "result2418_15.nsv", "result2418_16.nsv", "result2418_17.nsv", "result2418_18.nsv", "result2418_19.nsv", "result2418_20.nsv", "result2418_21.nsv"];
val thyn = "vfmTestDefs2418";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
