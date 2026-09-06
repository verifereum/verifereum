Theory vfmTest1767[no_sig_docs]
Ancestors vfmTestDefs1767
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1767_0.nsv", "result1767_1.nsv", "result1767_2.nsv", "result1767_3.nsv", "result1767_4.nsv", "result1767_5.nsv", "result1767_6.nsv", "result1767_7.nsv", "result1767_8.nsv", "result1767_9.nsv", "result1767_10.nsv", "result1767_11.nsv", "result1767_12.nsv", "result1767_13.nsv", "result1767_14.nsv", "result1767_15.nsv"];
val thyn = "vfmTestDefs1767";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
