Theory vfmTest2791[no_sig_docs]
Ancestors vfmTestDefs2791
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2791_0.nsv", "result2791_1.nsv", "result2791_2.nsv", "result2791_3.nsv"];
val thyn = "vfmTestDefs2791";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
