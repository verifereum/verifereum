Theory vfmTest2674[no_sig_docs]
Ancestors vfmTestDefs2674
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2674_0.nsv", "result2674_1.nsv", "result2674_2.nsv", "result2674_3.nsv"];
val thyn = "vfmTestDefs2674";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
