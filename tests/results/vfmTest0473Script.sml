Theory vfmTest0473[no_sig_docs]
Ancestors vfmTestDefs0473
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0473_0.nsv", "result0473_1.nsv", "result0473_2.nsv", "result0473_3.nsv", "result0473_4.nsv", "result0473_5.nsv", "result0473_6.nsv", "result0473_7.nsv", "result0473_8.nsv", "result0473_9.nsv", "result0473_10.nsv", "result0473_11.nsv", "result0473_12.nsv", "result0473_13.nsv", "result0473_14.nsv", "result0473_15.nsv", "result0473_16.nsv", "result0473_17.nsv", "result0473_18.nsv", "result0473_19.nsv", "result0473_20.nsv", "result0473_21.nsv", "result0473_22.nsv", "result0473_23.nsv", "result0473_24.nsv", "result0473_25.nsv", "result0473_26.nsv", "result0473_27.nsv", "result0473_28.nsv", "result0473_29.nsv", "result0473_30.nsv", "result0473_31.nsv", "result0473_32.nsv", "result0473_33.nsv", "result0473_34.nsv", "result0473_35.nsv", "result0473_36.nsv"];
val thyn = "vfmTestDefs0473";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
