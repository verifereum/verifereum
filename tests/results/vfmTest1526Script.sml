Theory vfmTest1526[no_sig_docs]
Ancestors vfmTestDefs1526
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1526_0.nsv", "result1526_1.nsv", "result1526_2.nsv", "result1526_3.nsv", "result1526_4.nsv", "result1526_5.nsv", "result1526_6.nsv", "result1526_7.nsv", "result1526_8.nsv", "result1526_9.nsv", "result1526_10.nsv", "result1526_11.nsv"];
val thyn = "vfmTestDefs1526";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
