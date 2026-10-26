Theory vfmTest0883[no_sig_docs]
Ancestors vfmTestDefs0883
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0883_0.nsv", "result0883_1.nsv", "result0883_2.nsv", "result0883_3.nsv", "result0883_4.nsv", "result0883_5.nsv", "result0883_6.nsv", "result0883_7.nsv", "result0883_8.nsv", "result0883_9.nsv", "result0883_10.nsv", "result0883_11.nsv", "result0883_12.nsv", "result0883_13.nsv", "result0883_14.nsv", "result0883_15.nsv", "result0883_16.nsv", "result0883_17.nsv", "result0883_18.nsv", "result0883_19.nsv", "result0883_20.nsv", "result0883_21.nsv", "result0883_22.nsv", "result0883_23.nsv", "result0883_24.nsv", "result0883_25.nsv", "result0883_26.nsv", "result0883_27.nsv", "result0883_28.nsv", "result0883_29.nsv"];
val thyn = "vfmTestDefs0883";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
