Theory vfmTest0710[no_sig_docs]
Ancestors vfmTestDefs0710
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0710_0.nsv", "result0710_1.nsv", "result0710_2.nsv", "result0710_3.nsv", "result0710_4.nsv", "result0710_5.nsv", "result0710_6.nsv", "result0710_7.nsv", "result0710_8.nsv", "result0710_9.nsv", "result0710_10.nsv", "result0710_11.nsv", "result0710_12.nsv", "result0710_13.nsv", "result0710_14.nsv", "result0710_15.nsv"];
val thyn = "vfmTestDefs0710";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
