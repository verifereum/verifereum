Theory vfmTest2954[no_sig_docs]
Ancestors vfmTestDefs2954
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2954_0.nsv", "result2954_1.nsv", "result2954_2.nsv", "result2954_3.nsv", "result2954_4.nsv", "result2954_5.nsv", "result2954_6.nsv", "result2954_7.nsv", "result2954_8.nsv", "result2954_9.nsv", "result2954_10.nsv", "result2954_11.nsv", "result2954_12.nsv", "result2954_13.nsv", "result2954_14.nsv", "result2954_15.nsv", "result2954_16.nsv"];
val thyn = "vfmTestDefs2954";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
