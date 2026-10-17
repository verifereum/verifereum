Theory vfmTest0168[no_sig_docs]
Ancestors vfmTestDefs0168
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0168_0.nsv", "result0168_1.nsv", "result0168_2.nsv", "result0168_3.nsv", "result0168_4.nsv", "result0168_5.nsv", "result0168_6.nsv", "result0168_7.nsv", "result0168_8.nsv", "result0168_9.nsv", "result0168_10.nsv", "result0168_11.nsv", "result0168_12.nsv", "result0168_13.nsv", "result0168_14.nsv", "result0168_15.nsv", "result0168_16.nsv", "result0168_17.nsv"];
val thyn = "vfmTestDefs0168";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
