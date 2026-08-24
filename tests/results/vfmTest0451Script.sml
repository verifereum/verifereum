Theory vfmTest0451[no_sig_docs]
Ancestors vfmTestDefs0451
Libs wordsLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0451_0.nsv", "result0451_1.nsv", "result0451_2.nsv", "result0451_3.nsv", "result0451_4.nsv", "result0451_5.nsv"];
val thyn = "vfmTestDefs0451";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
