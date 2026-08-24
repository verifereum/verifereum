Theory vfmTest0407[no_sig_docs]
Ancestors vfmTestDefs0407
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0407_0.nsv", "result0407_1.nsv", "result0407_2.nsv", "result0407_3.nsv", "result0407_4.nsv", "result0407_5.nsv", "result0407_6.nsv", "result0407_7.nsv", "result0407_8.nsv", "result0407_9.nsv", "result0407_10.nsv", "result0407_11.nsv", "result0407_12.nsv", "result0407_13.nsv", "result0407_14.nsv", "result0407_15.nsv", "result0407_16.nsv", "result0407_17.nsv", "result0407_18.nsv", "result0407_19.nsv", "result0407_20.nsv", "result0407_21.nsv", "result0407_22.nsv", "result0407_23.nsv", "result0407_24.nsv", "result0407_25.nsv", "result0407_26.nsv", "result0407_27.nsv", "result0407_28.nsv", "result0407_29.nsv"];
val thyn = "vfmTestDefs0407";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
