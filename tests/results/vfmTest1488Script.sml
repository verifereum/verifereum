Theory vfmTest1488[no_sig_docs]
Ancestors vfmTestDefs1488
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1488_0.nsv", "result1488_1.nsv", "result1488_2.nsv", "result1488_3.nsv", "result1488_4.nsv", "result1488_5.nsv", "result1488_6.nsv", "result1488_7.nsv", "result1488_8.nsv", "result1488_9.nsv", "result1488_10.nsv", "result1488_11.nsv", "result1488_12.nsv", "result1488_13.nsv", "result1488_14.nsv", "result1488_15.nsv", "result1488_16.nsv", "result1488_17.nsv", "result1488_18.nsv", "result1488_19.nsv", "result1488_20.nsv", "result1488_21.nsv", "result1488_22.nsv", "result1488_23.nsv", "result1488_24.nsv", "result1488_25.nsv", "result1488_26.nsv", "result1488_27.nsv", "result1488_28.nsv", "result1488_29.nsv", "result1488_30.nsv", "result1488_31.nsv", "result1488_32.nsv", "result1488_33.nsv", "result1488_34.nsv", "result1488_35.nsv"];
val thyn = "vfmTestDefs1488";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
