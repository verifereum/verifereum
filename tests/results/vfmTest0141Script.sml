Theory vfmTest0141[no_sig_docs]
Ancestors vfmTestDefs0141
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0141_0.nsv", "result0141_1.nsv", "result0141_2.nsv", "result0141_3.nsv", "result0141_4.nsv", "result0141_5.nsv", "result0141_6.nsv", "result0141_7.nsv", "result0141_8.nsv", "result0141_9.nsv", "result0141_10.nsv", "result0141_11.nsv", "result0141_12.nsv", "result0141_13.nsv", "result0141_14.nsv", "result0141_15.nsv"];
val thyn = "vfmTestDefs0141";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
