Theory vfmTest0230[no_sig_docs]
Ancestors vfmTestDefs0230
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0230_0.nsv", "result0230_1.nsv", "result0230_2.nsv", "result0230_3.nsv", "result0230_4.nsv", "result0230_5.nsv", "result0230_6.nsv", "result0230_7.nsv", "result0230_8.nsv", "result0230_9.nsv", "result0230_10.nsv", "result0230_11.nsv", "result0230_12.nsv", "result0230_13.nsv", "result0230_14.nsv", "result0230_15.nsv", "result0230_16.nsv", "result0230_17.nsv"];
val thyn = "vfmTestDefs0230";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
