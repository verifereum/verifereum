Theory vfmTest0080[no_sig_docs]
Ancestors vfmTestDefs0080
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0080_0.nsv", "result0080_1.nsv", "result0080_2.nsv", "result0080_3.nsv", "result0080_4.nsv", "result0080_5.nsv", "result0080_6.nsv", "result0080_7.nsv", "result0080_8.nsv", "result0080_9.nsv", "result0080_10.nsv", "result0080_11.nsv", "result0080_12.nsv", "result0080_13.nsv", "result0080_14.nsv", "result0080_15.nsv", "result0080_16.nsv", "result0080_17.nsv", "result0080_18.nsv", "result0080_19.nsv"];
val thyn = "vfmTestDefs0080";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
