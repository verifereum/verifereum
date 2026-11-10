Theory vfmTest1489[no_sig_docs]
Ancestors vfmTestDefs1489
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1489_0.nsv", "result1489_1.nsv", "result1489_2.nsv", "result1489_3.nsv", "result1489_4.nsv", "result1489_5.nsv", "result1489_6.nsv", "result1489_7.nsv", "result1489_8.nsv", "result1489_9.nsv", "result1489_10.nsv", "result1489_11.nsv", "result1489_12.nsv", "result1489_13.nsv", "result1489_14.nsv", "result1489_15.nsv", "result1489_16.nsv", "result1489_17.nsv", "result1489_18.nsv", "result1489_19.nsv", "result1489_20.nsv", "result1489_21.nsv", "result1489_22.nsv", "result1489_23.nsv", "result1489_24.nsv", "result1489_25.nsv", "result1489_26.nsv", "result1489_27.nsv", "result1489_28.nsv", "result1489_29.nsv", "result1489_30.nsv", "result1489_31.nsv", "result1489_32.nsv", "result1489_33.nsv", "result1489_34.nsv", "result1489_35.nsv"];
val thyn = "vfmTestDefs1489";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
