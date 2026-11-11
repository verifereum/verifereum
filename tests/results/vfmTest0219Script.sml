Theory vfmTest0219[no_sig_docs]
Ancestors vfmTestDefs0219
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0219_0.nsv", "result0219_1.nsv", "result0219_2.nsv", "result0219_3.nsv", "result0219_4.nsv", "result0219_5.nsv", "result0219_6.nsv", "result0219_7.nsv", "result0219_8.nsv", "result0219_9.nsv", "result0219_10.nsv", "result0219_11.nsv", "result0219_12.nsv", "result0219_13.nsv", "result0219_14.nsv", "result0219_15.nsv"];
val thyn = "vfmTestDefs0219";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
