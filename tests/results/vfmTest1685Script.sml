Theory vfmTest1685[no_sig_docs]
Ancestors vfmTestDefs1685
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1685_0.nsv", "result1685_1.nsv", "result1685_2.nsv", "result1685_3.nsv", "result1685_4.nsv", "result1685_5.nsv", "result1685_6.nsv", "result1685_7.nsv", "result1685_8.nsv", "result1685_9.nsv", "result1685_10.nsv", "result1685_11.nsv", "result1685_12.nsv", "result1685_13.nsv", "result1685_14.nsv", "result1685_15.nsv", "result1685_16.nsv", "result1685_17.nsv", "result1685_18.nsv", "result1685_19.nsv"];
val thyn = "vfmTestDefs1685";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
