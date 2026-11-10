Theory vfmTest1518[no_sig_docs]
Ancestors vfmTestDefs1518
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1518_0.nsv", "result1518_1.nsv", "result1518_2.nsv", "result1518_3.nsv", "result1518_4.nsv", "result1518_5.nsv", "result1518_6.nsv", "result1518_7.nsv", "result1518_8.nsv", "result1518_9.nsv", "result1518_10.nsv", "result1518_11.nsv", "result1518_12.nsv", "result1518_13.nsv", "result1518_14.nsv", "result1518_15.nsv", "result1518_16.nsv", "result1518_17.nsv", "result1518_18.nsv", "result1518_19.nsv", "result1518_20.nsv", "result1518_21.nsv", "result1518_22.nsv", "result1518_23.nsv"];
val thyn = "vfmTestDefs1518";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
