Theory vfmTest2926[no_sig_docs]
Ancestors vfmTestDefs2926
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2926_0.nsv", "result2926_1.nsv", "result2926_2.nsv", "result2926_3.nsv", "result2926_4.nsv", "result2926_5.nsv", "result2926_6.nsv", "result2926_7.nsv"];
val thyn = "vfmTestDefs2926";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
