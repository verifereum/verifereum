Theory vfmTest0279[no_sig_docs]
Ancestors vfmTestDefs0279
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0279_0.nsv", "result0279_1.nsv", "result0279_2.nsv", "result0279_3.nsv", "result0279_4.nsv", "result0279_5.nsv", "result0279_6.nsv", "result0279_7.nsv", "result0279_8.nsv", "result0279_9.nsv", "result0279_10.nsv", "result0279_11.nsv", "result0279_12.nsv", "result0279_13.nsv", "result0279_14.nsv", "result0279_15.nsv", "result0279_16.nsv", "result0279_17.nsv", "result0279_18.nsv", "result0279_19.nsv", "result0279_20.nsv", "result0279_21.nsv", "result0279_22.nsv", "result0279_23.nsv", "result0279_24.nsv", "result0279_25.nsv", "result0279_26.nsv", "result0279_27.nsv", "result0279_28.nsv", "result0279_29.nsv"];
val thyn = "vfmTestDefs0279";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
