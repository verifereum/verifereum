Theory vfmTest0949[no_sig_docs]
Ancestors vfmTestDefs0949
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0949_0.nsv", "result0949_1.nsv", "result0949_2.nsv", "result0949_3.nsv", "result0949_4.nsv", "result0949_5.nsv", "result0949_6.nsv", "result0949_7.nsv", "result0949_8.nsv", "result0949_9.nsv", "result0949_10.nsv", "result0949_11.nsv", "result0949_12.nsv", "result0949_13.nsv", "result0949_14.nsv", "result0949_15.nsv", "result0949_16.nsv", "result0949_17.nsv", "result0949_18.nsv", "result0949_19.nsv", "result0949_20.nsv", "result0949_21.nsv", "result0949_22.nsv", "result0949_23.nsv", "result0949_24.nsv", "result0949_25.nsv", "result0949_26.nsv", "result0949_27.nsv", "result0949_28.nsv", "result0949_29.nsv", "result0949_30.nsv", "result0949_31.nsv", "result0949_32.nsv", "result0949_33.nsv", "result0949_34.nsv", "result0949_35.nsv", "result0949_36.nsv", "result0949_37.nsv"];
val thyn = "vfmTestDefs0949";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
