Theory vfmTest2838[no_sig_docs]
Ancestors vfmTestDefs2838
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2838_0.nsv", "result2838_1.nsv", "result2838_2.nsv", "result2838_3.nsv"];
val thyn = "vfmTestDefs2838";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
