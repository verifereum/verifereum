Theory vfmTest0461[no_sig_docs]
Ancestors vfmTestDefs0461
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0461_0.nsv", "result0461_1.nsv", "result0461_2.nsv", "result0461_3.nsv", "result0461_4.nsv", "result0461_5.nsv", "result0461_6.nsv", "result0461_7.nsv", "result0461_8.nsv", "result0461_9.nsv", "result0461_10.nsv"];
val thyn = "vfmTestDefs0461";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
