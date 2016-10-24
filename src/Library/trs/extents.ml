% extents.ml                                            (c) R.J.Boulton 1990 %
%----------------------------------------------------------------------------%


%****************************************************************************%
%                                                                            %
%  W A R N I N G : The version of ML for which this code was written has     %
%                  equality on abstract types defined automatically, i.e.    %
%                  without the need for it to be defined within the          %
%                  abstract type definitions. Furthermore, this code makes   %
%                  use of these equality functions.                          %
%                                                                            %
%****************************************************************************%


%****************************************************************************%
%                                                                            %
%                            .....                                           %
%                            .M L.                                           %
%                            .....                                           %
%                              |                                             %
%                            ..|..                                           %
%                            .HOL.                                           %
%                            .....                                           %
%                              |                                             %
%                              |                                             %
%                          extents.ml______________                          %
%                              |                   |                         %
%                              |                   |                         %
%                           sets.ml                |                         %
%                              |                   |                         %
%                              |                   |                         %
%                          extract.ml        ______|______                   %
%                              |            |             |                  %
%                              |            |             |                  %
%                          struct.ml     name.ml     thmkind.ml              %
%                              |__________  |  ___________|                  %
%                                         | | |                              %
%                                      matching.ml                           %
%                                     ______|_______                         %
%                                    |              |                        %
%                               sidecond.ml     search.ml                    %
%                                    |_____   ______|                        %
%                                          | |                               %
%                                        user.ml                             %
%                                                                            %
%****************************************************************************%


%----------------------------------------------------------------------------%
