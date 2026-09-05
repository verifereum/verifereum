Theory vfmTest1690[no_sig_docs]
Ancestors vfmTestDefs1690
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1690_0.nsv", "result1690_1.nsv", "result1690_2.nsv", "result1690_3.nsv", "result1690_4.nsv", "result1690_5.nsv", "result1690_6.nsv", "result1690_7.nsv", "result1690_8.nsv", "result1690_9.nsv", "result1690_10.nsv", "result1690_11.nsv", "result1690_12.nsv", "result1690_13.nsv", "result1690_14.nsv", "result1690_15.nsv", "result1690_16.nsv", "result1690_17.nsv", "result1690_18.nsv", "result1690_19.nsv"];
val thyn = "vfmTestDefs1690";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
