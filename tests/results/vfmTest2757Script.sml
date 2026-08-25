Theory vfmTest2757[no_sig_docs]
Ancestors vfmTestDefs2757
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2757_0.nsv", "result2757_1.nsv", "result2757_2.nsv", "result2757_3.nsv"];
val thyn = "vfmTestDefs2757";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
