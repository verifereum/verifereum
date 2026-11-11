Theory vfmTest1635[no_sig_docs]
Ancestors vfmTestDefs1635
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1635_0.nsv", "result1635_1.nsv", "result1635_2.nsv", "result1635_3.nsv", "result1635_4.nsv", "result1635_5.nsv", "result1635_6.nsv", "result1635_7.nsv", "result1635_8.nsv", "result1635_9.nsv", "result1635_10.nsv", "result1635_11.nsv", "result1635_12.nsv", "result1635_13.nsv", "result1635_14.nsv", "result1635_15.nsv", "result1635_16.nsv", "result1635_17.nsv", "result1635_18.nsv", "result1635_19.nsv", "result1635_20.nsv", "result1635_21.nsv", "result1635_22.nsv", "result1635_23.nsv", "result1635_24.nsv", "result1635_25.nsv", "result1635_26.nsv", "result1635_27.nsv", "result1635_28.nsv", "result1635_29.nsv", "result1635_30.nsv", "result1635_31.nsv"];
val thyn = "vfmTestDefs1635";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
