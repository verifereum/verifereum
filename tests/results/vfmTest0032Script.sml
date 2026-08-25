Theory vfmTest0032[no_sig_docs]
Ancestors vfmTestDefs0032
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0032_0.nsv", "result0032_1.nsv", "result0032_2.nsv", "result0032_3.nsv", "result0032_4.nsv", "result0032_5.nsv", "result0032_6.nsv", "result0032_7.nsv", "result0032_8.nsv", "result0032_9.nsv", "result0032_10.nsv", "result0032_11.nsv", "result0032_12.nsv", "result0032_13.nsv", "result0032_14.nsv", "result0032_15.nsv", "result0032_16.nsv", "result0032_17.nsv", "result0032_18.nsv", "result0032_19.nsv", "result0032_20.nsv", "result0032_21.nsv", "result0032_22.nsv", "result0032_23.nsv"];
val thyn = "vfmTestDefs0032";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
