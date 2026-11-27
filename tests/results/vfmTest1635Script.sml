Theory vfmTest1635[no_sig_docs]
Ancestors vfmTestDefs1635
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1635_0.nsv", "result1635_1.nsv", "result1635_2.nsv", "result1635_3.nsv", "result1635_4.nsv", "result1635_5.nsv", "result1635_6.nsv", "result1635_7.nsv"];
val thyn = "vfmTestDefs1635";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
