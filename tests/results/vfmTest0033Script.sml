Theory vfmTest0033[no_sig_docs]
Ancestors vfmTestDefs0033
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0033_0.nsv", "result0033_1.nsv", "result0033_2.nsv", "result0033_3.nsv", "result0033_4.nsv", "result0033_5.nsv", "result0033_6.nsv", "result0033_7.nsv", "result0033_8.nsv", "result0033_9.nsv", "result0033_10.nsv", "result0033_11.nsv", "result0033_12.nsv", "result0033_13.nsv", "result0033_14.nsv", "result0033_15.nsv", "result0033_16.nsv", "result0033_17.nsv", "result0033_18.nsv", "result0033_19.nsv", "result0033_20.nsv", "result0033_21.nsv", "result0033_22.nsv", "result0033_23.nsv", "result0033_24.nsv", "result0033_25.nsv", "result0033_26.nsv", "result0033_27.nsv", "result0033_28.nsv", "result0033_29.nsv", "result0033_30.nsv", "result0033_31.nsv", "result0033_32.nsv", "result0033_33.nsv", "result0033_34.nsv", "result0033_35.nsv"];
val thyn = "vfmTestDefs0033";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
