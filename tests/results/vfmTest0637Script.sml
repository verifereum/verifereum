Theory vfmTest0637[no_sig_docs]
Ancestors vfmTestDefs0637
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0637_0.nsv", "result0637_1.nsv", "result0637_2.nsv", "result0637_3.nsv", "result0637_4.nsv", "result0637_5.nsv", "result0637_6.nsv", "result0637_7.nsv", "result0637_8.nsv", "result0637_9.nsv", "result0637_10.nsv", "result0637_11.nsv", "result0637_12.nsv", "result0637_13.nsv", "result0637_14.nsv", "result0637_15.nsv", "result0637_16.nsv", "result0637_17.nsv", "result0637_18.nsv", "result0637_19.nsv", "result0637_20.nsv", "result0637_21.nsv", "result0637_22.nsv", "result0637_23.nsv", "result0637_24.nsv", "result0637_25.nsv", "result0637_26.nsv", "result0637_27.nsv", "result0637_28.nsv", "result0637_29.nsv", "result0637_30.nsv", "result0637_31.nsv", "result0637_32.nsv", "result0637_33.nsv", "result0637_34.nsv", "result0637_35.nsv"];
val thyn = "vfmTestDefs0637";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
