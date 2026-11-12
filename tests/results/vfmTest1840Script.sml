Theory vfmTest1840[no_sig_docs]
Ancestors vfmTestDefs1840
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result1840_0.nsv", "result1840_1.nsv", "result1840_2.nsv", "result1840_3.nsv", "result1840_4.nsv", "result1840_5.nsv", "result1840_6.nsv", "result1840_7.nsv", "result1840_8.nsv", "result1840_9.nsv"];
val thyn = "vfmTestDefs1840";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
