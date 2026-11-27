Theory vfmTest0600[no_sig_docs]
Ancestors vfmTestDefs0600
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0600_0.nsv", "result0600_1.nsv", "result0600_2.nsv", "result0600_3.nsv", "result0600_4.nsv", "result0600_5.nsv", "result0600_6.nsv", "result0600_7.nsv", "result0600_8.nsv", "result0600_9.nsv", "result0600_10.nsv", "result0600_11.nsv", "result0600_12.nsv", "result0600_13.nsv", "result0600_14.nsv", "result0600_15.nsv", "result0600_16.nsv", "result0600_17.nsv", "result0600_18.nsv", "result0600_19.nsv", "result0600_20.nsv", "result0600_21.nsv", "result0600_22.nsv", "result0600_23.nsv", "result0600_24.nsv", "result0600_25.nsv", "result0600_26.nsv", "result0600_27.nsv", "result0600_28.nsv", "result0600_29.nsv"];
val thyn = "vfmTestDefs0600";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
