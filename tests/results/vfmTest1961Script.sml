Theory vfmTest1961[no_sig_docs]
Ancestors vfmTestDefs1961
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1961_0.nsv", "result1961_1.nsv", "result1961_2.nsv", "result1961_3.nsv", "result1961_4.nsv", "result1961_5.nsv", "result1961_6.nsv", "result1961_7.nsv", "result1961_8.nsv", "result1961_9.nsv"];
val thyn = "vfmTestDefs1961";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
