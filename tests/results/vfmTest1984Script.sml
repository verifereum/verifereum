Theory vfmTest1984[no_sig_docs]
Ancestors vfmTestDefs1984
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1984_0.nsv", "result1984_1.nsv", "result1984_2.nsv", "result1984_3.nsv", "result1984_4.nsv", "result1984_5.nsv", "result1984_6.nsv", "result1984_7.nsv", "result1984_8.nsv", "result1984_9.nsv"];
val thyn = "vfmTestDefs1984";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
