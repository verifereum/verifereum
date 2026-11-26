Theory vfmTest1503[no_sig_docs]
Ancestors vfmTestDefs1503
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1503_0.nsv", "result1503_1.nsv", "result1503_2.nsv", "result1503_3.nsv", "result1503_4.nsv", "result1503_5.nsv", "result1503_6.nsv", "result1503_7.nsv", "result1503_8.nsv", "result1503_9.nsv", "result1503_10.nsv", "result1503_11.nsv", "result1503_12.nsv", "result1503_13.nsv", "result1503_14.nsv", "result1503_15.nsv", "result1503_16.nsv", "result1503_17.nsv", "result1503_18.nsv", "result1503_19.nsv", "result1503_20.nsv", "result1503_21.nsv", "result1503_22.nsv", "result1503_23.nsv", "result1503_24.nsv", "result1503_25.nsv", "result1503_26.nsv", "result1503_27.nsv", "result1503_28.nsv", "result1503_29.nsv", "result1503_30.nsv", "result1503_31.nsv", "result1503_32.nsv", "result1503_33.nsv", "result1503_34.nsv", "result1503_35.nsv"];
val thyn = "vfmTestDefs1503";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
