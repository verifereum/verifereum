Theory vfmTest0417[no_sig_docs]
Ancestors vfmTestDefs0417
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0417_0.nsv", "result0417_1.nsv", "result0417_2.nsv", "result0417_3.nsv", "result0417_4.nsv", "result0417_5.nsv", "result0417_6.nsv", "result0417_7.nsv", "result0417_8.nsv", "result0417_9.nsv", "result0417_10.nsv", "result0417_11.nsv", "result0417_12.nsv", "result0417_13.nsv", "result0417_14.nsv", "result0417_15.nsv", "result0417_16.nsv", "result0417_17.nsv", "result0417_18.nsv", "result0417_19.nsv", "result0417_20.nsv", "result0417_21.nsv", "result0417_22.nsv", "result0417_23.nsv", "result0417_24.nsv", "result0417_25.nsv", "result0417_26.nsv", "result0417_27.nsv", "result0417_28.nsv", "result0417_29.nsv", "result0417_30.nsv", "result0417_31.nsv", "result0417_32.nsv", "result0417_33.nsv", "result0417_34.nsv", "result0417_35.nsv", "result0417_36.nsv"];
val thyn = "vfmTestDefs0417";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
